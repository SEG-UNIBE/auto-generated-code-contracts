# Build srcML for a Specific Ubuntu Version

- Install Docker [Desktop](https://www.docker.com/products/docker-desktop/).
- In the ```Dockerfile``` set the Ubuntu version of the target system, e.g., ```FROM ubuntu:22.04```.

```
cd <this folder>
docker-compose up
```

- The binaries ```srcml``` and ```libsrcml.so.1``` will be written to the ```build``` folder.
- To remove the container.

```
docker-compose down
```

- Copy the  ```build``` folder to the target system.
- Run the installation sript on the target Ubuntu system.

```
cd <build folder>`
sudo bash install_srcml.sh
```